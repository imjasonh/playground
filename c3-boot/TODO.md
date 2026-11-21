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
