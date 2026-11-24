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

### Done

- `c3-verify` has `json` (strict and canonical JSON), `tuf` (the C3TU
  container, the root chain, and `targets.json`), `trusted_root` (Fulcio,
  Rekor, and TSA keys into a `TrustRoot`), and `tuf_slot::accept_slot`.
  The genesis keys, `keys`, `chain`, the trust-root blob decoder, and
  `accept` are gone, and `TrustRoot` holds up to 8 Fulcio intermediates,
  16 Ed25519 logs, and 8 TSAs.
- The slot manifest is version 2, with one `tuf` part of up to 24,576
  bytes in place of `chain` and `blob`. The QEMU scenarios, the mutation
  tests, and the fuzz seeds build version 2 slots.
- `testdata/keys/` holds the seeds of a development TUF repository
  (`c3-ota tuf-dev-root` and `tuf-dev-targets`), and
  `tuf-dev-root.json` is its root version 1.
- The bootloader compiles in the root that `C3_TUF_ROOT` names (`dev` for
  the development root) and the identity policy file that `C3_POLICY`
  names (`release/policy` by default), and a production root requires
  `C3_EFUSE_BURN=on`. It holds the whole TUF part, the bundle, and a
  20,544-byte key buffer, 61,780 bytes of buffers in all; the QEMU
  scenarios peak at 78,540 bytes of stack, and the linker requires 80 KiB.
- `efuse::lock()` makes the eFuse controller read-only with region
  permission control, and eFuse programming sets ESP-IDF's timing. Both
  need checking on a board.
- The pinned image is the production build: Sigstore's root 16
  (`release/pinned-root.json`), `release/policy`, and eFuse burns.
  `bootloader/dev-image.sha256` pins its digest.
- `c3-release.yml` packages the roots after the pinned one, `targets.json`,
  and `trusted_root.json` from `testdata/tuf/` with
  `release/package-tuf.sh`, which runs `tuf-verify`, before it signs.
  `c3-trust-root.yml` refreshes `testdata/tuf/` and `release/`. `c3-ota
  link`, `blob`, `chain`, and `pubkey` are gone.

### Remaining

1. **Proofs.** Regenerate `Image/Bootloader*.lean` with
   `scripts/extract-functions.py` and the generated proofs with their
   `gen-*.py` scripts, and rework the hand-written machine-code proofs
   whose functions moved. `TrustRoot`'s layout changed with the new caps.
   Retire `Spec/TrustRoot.lean`, `Theorems/TrustRoot.lean`, the proofs for
   `chain`, `keys`, and `trustroot`, and `lake exe trust-check`. Update
   `lake exe spec-vectors` and `decode-check` for manifest version 2, and
   `tuf-check` and `sigstore-check` for the cases `c3-ota` added. Prove
   that the machine code of `json::parse`, `tuf::verify`,
   `trusted_root::extract`, and `tuf_slot::accept_slot` computes the new
   specifications, prove properties of the specifications (a canonical
   document re-encodes to itself; an accepted chain has a threshold of
   signatures under each root), and restate the headline theorem from the
   pinned TUF root and the compiled-in policy. Rebuild the boot lockstep
   scenarios.
2. **Hardware.** Check `efuse::lock()` and the eFuse timing on a board.

### Decisions

- **Chain growth.** When the root chain in a slot grows too long, re-pin a
  newer root with a USB bootloader reflash. The device keeps no writable
  trusted root.
- **Expiry.** Keep the current rule: only the final root's and
  `targets.json`'s expiry count, and a slot signed before expiry stays
  bootable.
- **Limits.** Raise the caps to 8 Fulcio intermediates, 16 Ed25519 logs,
  and 8 TSAs in the cutover rebuild, which regenerates `sigstore::verify`'s
  proofs anyway, and keep rejecting a trusted root that exceeds them.
  Skipping entries could drop the one an older release needs. Sigstore
  keeps rotated-out entries listed, so the count only grows; exceeding the
  new caps calls for a USB reflash, like a long chain.
- **Development root.** Use generated seeds, as in step 2.

Key types remain a known limit: roots 1 through 4 use hex ECDSA keys,
which the device doesn't decode, and Rekor's P-256 log and any non-P-384
certificate authority are skipped. A change in Sigstore's key types stops
OTA until a USB reflash.
